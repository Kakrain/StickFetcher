import platform, sys,math
from numpy import fft,arange, sin, pi
from scipy import signal as sign
import numpy as np 
import time
from Tkinter import *
import ntpath
import tkMessageBox
from PIL import Image, ImageDraw, ImageTk
import os
from matplotlib.figure import Figure
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2TkAgg
import threading
import thread
import ttk
import csv
import signal
from cStringIO import StringIO
from struct import unpack
from tkFileDialog import askopenfilename, asksaveasfilename  
import cv2
import gc
from mpl_toolkits.mplot3d import Axes3D
import matplotlib.pyplot as plt
if platform.system() == 'Windows':
    if sys.maxsize > 2**32:
        sys.path.insert(1, r'./../functions/btk/win64')
    else:
        sys.path.insert(1, r'./../functions/btk/win32')
elif platform.system() == 'Linux':
    if sys.maxsize > 2**32:
        sys.path.insert(1, r'./../functions/btk/linux64')
    else:
        sys.path.insert(1, r'./../functions/btk/linux32')
elif platform.system() == 'Darwin':
    sys.path.insert(1, r'./../functions/btk/mac')
import btk
import matplotlib.pyplot as plt
def getFloat(floatStr,processor):
    "16-bit float string to number conversion"
    if processor > 1: #DEC or SGI
        floatNumber = unpack('f',floatStr[2:] + floatStr[0:2])[0]/4
    else:
        floatNumber = unpack('f',floatStr)[0]
    return floatNumber

class Animation(object):
    videolen=-1
    videoi=-1
    videoframe=0
    video=0
    videostring=0
    filename=""
    Hradius=15
    Eradius=3
    normh=0
    normw=0
    sep=12
    kineticGraph=0
    lagunaGraph=0
    curves=[]
    raw=[]
    frames=[]
    scale=-0.1
    toremove=0
    currenti=0
    frameRate=0
    colors=["blue","red","green","orange","black","brown","cyan","purple"]
    strokesraw=[4,9,16,23,27,34]
    framesc3d=[]
    strokes=[4,9,16,23,27,34]##2 primeros son los ojos
    currenti=0
    slidei=0
    linked=False
    tomerge=[]
    estadisticas=[]
    matrices=0
    tomerge.append([0,1])
    tomerge.append([2,1])
    tomerge.append([4,4])
    tomerge.append([11,3])
    tomerge.append([18,3])
    tomerge.append([23,3])
    tomerge.append([30,3])
    tomerge.append([37,3])
    video=0
    def setVideo(self,vid):
        self.video=vid
    def __init__(self,filename,onmarch,waits,value):
        self.videolen=-1
        self.videoi=-1
        self.videoframe=0
        self.video=0
        self.videostring=0
        if filename==None:
            return
        self.normh=200
        self.normw=15
        self.strokes=[1,2,3,7,11,12,16]
        self.video=0
        self.matrices=[]
        self.toremove=[]
        self.currenti=0
        filename=str(filename)
        self.filename=filename
        fid = open(filename, 'rb')       # open file for reading in binary format
        bytes = fid.read(512)
        buf = StringIO(bytes)
        firstBlockParameterSection, fmt = unpack('BB', buf.read(2))
        firstBlockByte = 512*(firstBlockParameterSection - 1) + 2
        fid.seek(firstBlockByte)
        nparameter_blocks, processor = unpack('BB', fid.read(2))
        processor = processor - 83
        buf.read(18)
        self.frameRate = getFloat(buf.read(4), processor)        
        reader = btk.btkAcquisitionFileReader()
        reader.SetFilename(filename)
        acq = reader.GetOutput()
        acq.Update()
        self.raw=np.empty((3, acq.GetPointFrameNumber(), 1))
        for i in range(0, acq.GetPoints().GetItemNumber()):
            label = acq.GetPoint(i).GetLabel()
            self.raw = np.dstack((self.raw, acq.GetPoint(label).GetValues().T))
        self.raw = self.raw.T
        self.raw = np.delete(self.raw, 0, axis=0)
        self.raw[self.raw==0] = np.NaN
        if(onmarch):
            self.preparar()
        else:
            self.procesar()
            self.simplify()
            self.decompose()
            self.splineCurvas(waits,value)
    def getRaw(self,i):
        i=i+1
        frame=[]
        for xi in self.raw:
            x, y, z = xi[:i].T
            vec=[self.scale*float(x[-1:]),self.scale*float(y[-1:]),self.scale*float(z[-1:])]
            frame.append(vec)
        return frame
    def preparar(self):
        for i in range(-90,90,5):
            self.matrices.append(rotation_matrix([0,0,1],i*math.pi/180))
        self.initialrotation=rotation_matrix([1,0,0],math.pi/2)
        self.kineticGraph=GraphOnMarch()
        self.lagunaGraph=GraphOnMarch()
        for h in range(0,len(self.tomerge)):
            for g in range(1,self.tomerge[h][1]+1):
                self.toremove.append(self.tomerge[h][0]+g)
    def procesarRawActual(self,rawframe):
        self.frames.append(rawframe)
        self.framesc3d.append(rawframe[:]) 
        spf=1/self.frameRate
        self.centrarFrame(self.currenti)
##        self.corregirRotacionFrame(self.currenti,self.matrices)
        self.homologarEscalaFrame(self.currenti)
##        
##        self.kineticGraph.addValue(kineticEnergy(self.framesc3d[self.currenti][:],self.framesc3d[self.currenti-1][:],spf))
##        self.lagunaGraph.addValue(kineticEnergy(self.framesc3d[self.currenti][:],self.framesc3d[0][:],spf))
    def simplifyFrame(self,num):
        frame=self.frames[num]
        for i in range(0,len(frame)):
            for h in range(0,len(self.tomerge)):
                if(i==self.tomerge[h][0]):
                    for g in range(1,self.tomerge[h][1]+1):
                        frame[i][0]+=frame[i+g][0]
                        frame[i][1]+=frame[i+g][1]
                        frame[i][2]+=frame[i+g][2]
                    frame[i][0]/=self.tomerge[h][1]+1
                    frame[i][1]/=self.tomerge[h][1]+1
                    frame[i][2]/=self.tomerge[h][1]+1
        newframe=[]
        for j in range(0,len(frame)):
            if (not(j in self.toremove)):
                newframe.append(frame[j])
        

        for frame in self.frames:
            for i in range(0,3):
                newframe[1][i]+=newframe[0][i]
                newframe[1][i]/=2

        self.frames[num]=newframe
    def isAnimationFinished(self):
        return self.currenti>len(self.raw[0])-2
    def nextFrame(self):
        if self.isAnimationFinished():
            return
        if(self.currenti==len(self.curves) and len(self.curves)!=len(self.raw[0]-2)):
            rawframe=self.getRaw(self.currenti)
            self.procesarRawActual(rawframe)
            self.simplifyFrame(self.currenti)
            self.decomposeFrame(self.currenti)
            self.splineCurva(self.currenti,2,10)
            
        self.dibujarFrame(self.slidei)
        self.dibujarCurva(self.currenti)
        self.dibujarVideo(self.currenti)
        self.dibujarProgreso()

    def homologarEscalaFrame(self,num):
        frame=self.frames[num]
        h=self.getHeigthFrame(frame)
        w=math.sqrt(((frame[8][1]-frame[4][1])**2)+((frame[8][0]-frame[4][0])**2)+((frame[8][2]-frame[4][2])**2))
        self.reescalarFrame(num,self.normh/h,self.normw/w)
    def reescalarFrame(self,num,sch,scxy):
        for i in range(0,len(self.frames[num])):
            self.frames[num][i][0]*=scxy
            self.framesc3d[num][i][0]*=scxy
            self.frames[num][i][1]*=scxy
            self.framesc3d[num][i][1]*=scxy
            self.frames[num][i][2]*=sch
            self.framesc3d[num][i][2]*=sch
            
    def splineCurva(self,num,k=3,N=100):    
        for i in range(2,len(self.curves[num])):
            points = np.array(self.curves[num][i])
            self.curves[num][i]=BezierSpline(points,k,N)
    def getVideoFrame(self,num):
        q=float(num)/len(self.raw[0])-1
        q=min(int(q*self.videolen),self.videolen)
        if(self.videoi>q):
            self.video.release()
            self.video=cv2.VideoCapture(self.videostring)
            self.videoi=0
            
            image=self.video.read()
            image=image[1]
            im = Image.fromarray(image)
            im = ImageTk.PhotoImage(image=im)
            self.videoframe=im
    
            return self.getVideoFrame(num)
        if(self.videoi==q):
            return self.videoframe
        while self.videoi<q:
            image=self.video.read()
            self.videoi+=1
        image=image[1]
        im = Image.fromarray(image)
        im = ImageTk.PhotoImage(image=im)
        self.videoframe=im
        return self.videoframe
    def dibujarVideo(self,num):
        if(self.videolen==0):
            labelvideo.config(text="este es un video",image="")
            return
        im=self.getVideoFrame(num)
        labelvideo.config(text="",image=im)
        
    def procesar(self):
        kineticdiff=[]
        lagunadiff=[]
        i=1
        frameAnt=0
        while i<len(self.raw[0]):
            frame=[]
            framec3d=[]
            for xi in self.raw:
                x, y, z = xi[:i].T
                vec=[self.scale*float(x[-1:]),self.scale*float(y[-1:]),self.scale*float(z[-1:])]
                frame.append(vec)
                framec3d.append(vec[:])
            if(i==1):
                frameAnt = frame[:]
            else:
                v=kineticEnergy(frame[:],frameAnt[:],1/self.frameRate)
                kineticdiff.append(v)
                lagunadiff.append(v)
                frameAnt = frame[:]
            i+=1
            
            self.frames.append(frame)
            self.framesc3d.append(framec3d)
        self.kineticGraph=GraphOnMarch()
        self.kineticGraph.setValues(kineticdiff)
        self.lagunaGraph=GraphOnMarch()
        self.lagunaGraph.setValues(lagunadiff)
##        self.kineticGraph=Graph(kineticdiff,self)
##        self.lagunaGraph=Graph(lagunadiff,self)
        self.homologarPosicion()
##        self.homologarRotacion()
    def getCenter(self):
        n=0
        xyz=[0,0,0]
        for frame in self.frames:
            for p in frame:
                xyz[0]+=p[0]
                xyz[1]+=p[1]
                xyz[2]+=p[2]
                n+=1
        xyz[0]=xyz[0]/n
        xyz[1]=xyz[1]/n
        xyz[2]=xyz[2]/n
        return xyz
    def getCenterFrame(self,num):
        n=0
        xyz=[0,0,0]
        for p in self.frames[num]:
            xyz[0]+=p[0]
            xyz[1]+=p[1]
            xyz[2]+=p[2]
            n+=1
        xyz[0]=xyz[0]/n
        xyz[1]=xyz[1]/n
        xyz[2]=xyz[2]/n
        return xyz
    def simplify(self):
        self.strokes=[1,2,3,7,11,12,16]
        toremove=[]
        data=[]
        for h in range(0,len(self.tomerge)):
            for g in range(1,self.tomerge[h][1]+1):
                toremove.append(self.tomerge[h][0]+g)
        for frame in self.frames:
            for i in range(0,len(frame)):
                for h in range(0,len(self.tomerge)):
                    if(i==self.tomerge[h][0]):
                        for g in range(1,self.tomerge[h][1]+1):
                            frame[i][0]+=frame[i+g][0]
                            frame[i][1]+=frame[i+g][1]
                            frame[i][2]+=frame[i+g][2]
                        frame[i][0]/=self.tomerge[h][1]+1
                        frame[i][1]/=self.tomerge[h][1]+1
                        frame[i][2]/=self.tomerge[h][1]+1
        for frame in self.frames:
            newframe=[]
            for j in range(0,len(frame)):
                if (not(j in toremove)):
                    newframe.append(frame[j])
            data.append(newframe)
        self.frames=data
        for frame in self.frames:
            for i in range(0,3):
                frame[1][i]+=frame[0][i]
                frame[1][i]/=2
    def getFrame2D(self,num):
        return self.framesc3d[num][:,1:3]
    def getCurva2D(self,num):
        newcurve=[]
        for i in range(2,len(self.curves[num])):
            newcurve.append(np.array(self.curves[num][i])[:,1:3])
        return np.array(newcurve)         
    def dibujarFrame(self,num):
        pi=0
        gi=0
        if (num<0):
            num=0
        global primera
        primera=0
        i=0
        
        for p in self.framesc3d[num]:
            point=[int(p[1])+vision.canvas.winfo_width()/2,int(p[2])+vision.canvas.winfo_height()/2]
            drawLines(point,self.colors[gi])
            drawOvals(point,self.colors[gi])
            pi+=1
            i+=1
            if(gi<len(self.strokesraw) and pi==self.strokesraw[gi]):
                primera=0
                gi+=1
    def decompose(self):
        for frame in self.frames:
            pi=0
            gi=0
            curveframe=[]
            curve=[]
            for p in frame:
                curve.append(p)
                pi+=1
                if(gi<len(self.strokes) and pi==self.strokes[gi]):
                    curveframe.append(curve[:])
                    curve=[]
                    gi+=1
            curveframe.append(curve[:])
            self.curves.append(curveframe)
        for curves in self.curves:
            ##merging the second and fifth point
            curves[2].append(curves[5][0])
            del curves[5]
            
            ##adding the neck point
            dx=curves[2][0][0]-curves[1][0][0]
            dy=curves[2][0][1]-curves[1][0][1]
            dz=curves[2][0][2]-curves[1][0][2]
            mv=math.sqrt(dx**2+dy**2+dz**2)
            t=self.Hradius/mv
            x=curves[1][0][0]+t*dx
            y=curves[1][0][1]+t*dy
            z=curves[1][0][2]+t*dz
            curves[2].insert(0,[x,y,z])

            ##adding joint points between arms and torso
            curves[3].insert(0,curves[2][0][:])
            curves[4].insert(0,curves[2][0][:])

            ##adding joint points between legs and torso
            curves[5].insert(0,curves[2][len(curves[2])-1][:])
            curves[6].insert(0,curves[2][len(curves[2])-1][:])

    def decomposeFrame(self,num):
        pi=0
        gi=0
        curveframe=[]
        curve=[]
        for p in self.frames[num]:
            curve.append(p)
            pi+=1
            if(gi<len(self.strokes) and pi==self.strokes[gi]):
                curveframe.append(curve[:])
                curve=[]
                gi+=1
        curveframe.append(curve[:])
        self.curves.append(curveframe)
        
        self.curves[num]

        self.curves[num][2].append(self.curves[num][5][0])
        del self.curves[num][5]
            
        ##adding the neck point
        dx=self.curves[num][2][0][0]-self.curves[num][1][0][0]
        dy=self.curves[num][2][0][1]-self.curves[num][1][0][1]
        dz=self.curves[num][2][0][2]-self.curves[num][1][0][2]
        mv=math.sqrt(dx**2+dy**2+dz**2)
        t=self.Hradius/mv
        x=self.curves[num][1][0][0]+t*dx
        y=self.curves[num][1][0][1]+t*dy
        z=self.curves[num][1][0][2]+t*dz
        self.curves[num][2].insert(0,[x,y,z])

        ##adding joint points between arms and torso
        self.curves[num][3].insert(0,self.curves[num][2][0][:])
        self.curves[num][4].insert(0,self.curves[num][2][0][:])

        ##adding joint points between legs and torso
        self.curves[num][5].insert(0,self.curves[num][2][len(self.curves[num][2])-1][:])
        self.curves[num][6].insert(0,self.curves[num][2][len(self.curves[num][2])-1][:])

        
    def dibujarProgreso(self,i):
        vision.canvas.create_text(vision.canvas.winfo_width()/2, vision.canvas.winfo_height()-10, text=str(i)+'/'+str(len(self.frames)-1))          
    def dibujarCurva(self,num):
        if (num<0):
            num=0
        global primera
        p=self.curves[num][1][0]
        point=[int(p[1])+vision.canvas.winfo_width()/2,int(p[2])+vision.canvas.winfo_height()/2]
        drawEmptyOval(point,self.Hradius,self.colors[1])

        s=self.sep
        p=self.curves[num][0][0]
        s=(1-(abs(p[1]-self.curves[num][1][0][1])/self.Hradius))*s
        point=[int(p[1])+vision.canvas.winfo_width()/2+int(s/2),int(p[2])+vision.canvas.winfo_height()/2]
        drawEmptyOval(point,self.Eradius,self.colors[0])

        point=[int(p[1])+vision.canvas.winfo_width()/2-int(s/2),int(p[2])+vision.canvas.winfo_height()/2]
        drawEmptyOval(point,self.Eradius,self.colors[0])
        for i in range(2,len(self.curves[num])):
            primera=0
            for p in self.curves[num][i]:
                point=[int(p[1])+vision.canvas.winfo_width()/2,int(p[2])+vision.canvas.winfo_height()/2]
                drawLines(point,self.colors[i])
    def splineCurvas(self,waits,val,k=3,N=10):
        for i in range(len(self.curves)):
            waits.avanzar(val*(100.0/len(self.curves)),"extrapolando puntos")
            self.splineCurva(i,k,N)
    def splineCurva(self,n,k=3,N=100):
        for curves in self.curves[n]:
            for i in range(2,len(curves)):
                points = np.array(curves[i])
                curves[i]=BezierSpline(points,k,N)
    def savePose(self,num):
        archivo = open("pose"+str(num)+".txt", 'w')
        for p in self.frames[num]:
            archivo.write(str(p[0])+"/"+str(p[1])+"/"+str(p[2])+"@")
        archivo.close()
    def drawKeyFramesWithCurves(self,w):
        w.delete("all")
        j=0
        global primera
        for i in self.keyframes:
           primera=0
           pi=0
           gi=0
           frame=[]
           j+=1
           p=self.curves[i][1][0]
           point=[int(p[1])+(j-((j>(len(self.keyframes)/2))*(len(self.keyframes)/2)))*1.1*canvas_width/len(self.keyframes),int(p[2])+(canvas_height/(2-(j>(len(self.keyframes)/2))))]
           drawEmptyOval(point,self.Hradius,self.colors[1])
           s=self.sep
           p=self.curves[i][0][0]
           s=(1-(abs(p[1]-self.curves[i][1][0][1])/self.Hradius))*s
           point=[int(p[1])+int(s/2)+(j-((j>len(self.keyframes)/2)*len(self.keyframes)/2))*1.1*canvas_width/len(self.keyframes),int(p[2])+(canvas_height/(2-(j>len(self.keyframes)/2)))]
           drawEmptyOval(point,self.Eradius,self.colors[0])
           point=[int(p[1])-int(s/2)+(j-((j>len(self.keyframes)/2)*len(self.keyframes)/2))*1.1*canvas_width/len(self.keyframes),int(p[2])+(canvas_height/(2-(j>len(self.keyframes)/2)))]
           drawEmptyOval(point,self.Eradius,self.colors[0])
           for k in range(1,len(self.curves[i])):
               primera=0
               for p in self.curves[i][k]:
                   point=[int(p[1])+(j-((j>len(self.keyframes)/2)*len(self.keyframes)/2))*1.1*canvas_width/len(self.keyframes),int(p[2])+(canvas_height/(2-(j>len(self.keyframes)/2)))]
                   drawLines(point,self.colors[k])
           w.update()
    def drawKeyFrames(self,w):
        w.delete("all")
        j=0
        global primera
        for i in self.keyframes:
           primera=0
           pi=0
           gi=0
           frame=[]
           j+=1
           for p in self.frames[i]:
                point=[int(p[1])+(j-((j>len(self.keyframes)/2)*len(self.keyframes)/2))*1.9*canvas_width/len(self.keyframes),int(p[2])+(canvas_height/(2-(j>len(self.keyframes)/2)))]
                drawLines(point,self.colors[gi])
                drawOvals(point,self.colors[gi])
                pi+=1
                if(gi<6 and pi==self.strokes[gi]):
                    primera=0
                    gi+=1
        w.update()
    def saveImageFile(self,num):
        black = (0, 0, 0)
        white=(255,255,255)
        image = Image.new("RGB", (canvas_width, canvas_height), white)
        draw = ImageDraw.Draw(image)
        if (num<0):
            num=0
        global primera
        p=self.curves[num][1][0]
        point=[int(p[1])+canvas_width/2,int(p[2])+canvas_height/2]
        drawEmptyOvalImage(point,self.Hradius,3,draw,black)
        s=self.sep
        p=self.curves[num][0][0]
        s=(1-(abs(p[1]-self.curves[num][1][0][1])/self.Hradius))*s
        point=[int(p[1])+int(s/2)+canvas_width/2,int(p[2])+canvas_height/2]
        drawEmptyOvalImage(point,self.Eradius,3,draw,black)
        point=[int(p[1])-int(s/2)+canvas_width/2,int(p[2])+canvas_height/2]
        drawEmptyOvalImage(point,self.Eradius,3,draw,black)
        for i in range(1,len(self.curves[num])):
            primera=0
            pi=0
            gi=0
            for p in self.curves[num][i]:  
                point=[int(p[1])+canvas_width/2,int(p[2])+canvas_height/2]
                drawLinesImage(draw,point,black)
                pi+=1
        filename = "pose"+str(num)+".jpg"
        image.save(filename)
        os.startfile(filename)
    def dibujar_curvas(self,canvas):
        global playing
        playing=True
        self.currenti=0
        thread = threading.Thread(target=self.dibujar_curvas_loop(canvas))
        thread.daemon = True 
        thread.start()
    def dibujar(self,canvas):
        global playing
        playing=True
        self.currenti=0
        thread = threading.Thread(target=self.dibujar_loop(canvas))
        thread.daemon = True 
        thread.start()
    def rotar(self,axis,theta):
        frame=self.framesc3d[self.slidei]
        for i in range(0,len(frame)):
            frame[i]=np.dot(rotation_matrix(axis,theta),frame[i])
    def transladar(self,vector):
        for frame in self.framesc3d:
            for p in frame:
                for i in range(0,len(p)):
                    p[i]+=vector[i]
    def homologarRotacion(self):
        matrices=[]
        for i in range(-90,90,5):
            matrices.append(rotation_matrix([0,0,1],i*math.pi/180))
        for i in range(len(self.frames)):
            self.corregirRotacionFrame(i,matrices)
##            self.corregirRotacionFrame2(i)
        
    def getAngleOffset(self,num):
        p1=0
        p2=0
        maxd=0
        v=[0,0]
        for i in range(0,len(self.frames[num])):
            for j in range(i+1,len(self.frames[num])):
                dist=(self.frames[num][i][0]-self.frames[num][j][0])**2+(self.frames[num][i][1]-self.frames[num][j][1])**2
                if(dist>maxd):
                    maxd=dist
                    p1=i
                    p2=j
        v[0]=(self.frames[num][p2][1]-self.frames[num][p1][1])
        v[1]=(self.frames[num][p2][0]-self.frames[num][p1][0])
        return math.atan(v[1]/v[0])
##        return math.atan2(v[1],v[0])
    def ponerFrenteFrame(self,num):
        v=[0,0]
        v[0]=(self.frames[num][8][1]-self.frames[num][4][1])
        v[1]=(self.frames[num][8][0]-self.frames[num][4][0])
        angle=-math.atan2(v[1],v[0])
        matrix=rotation_matrix([0,0,1],angle)
        self.framesc3d[num]=self.rotarFrame(self.framesc3d[num],matrix)
        self.frames[num]=self.rotarFrame(self.frames[num],matrix)
    def ponerFrenteTodos(self):
        for i in range(len(self.frames)):
            self.ponerFrenteFrame(i)
    def corregirRotacionFrame2(self,num):
        angle=-self.getAngleOffset(num)
        matrix=rotation_matrix([0,0,1],angle)
        self.framesc3d[num]=self.rotarFrame(self.framesc3d[num],matrix)
        self.frames[num]=self.rotarFrame(self.frames[num],matrix)
    def corregirRotacionFrame(self,num,matrices):
        maxw=0
        besti=0
        for i in range(len(matrices)):
            width=self.getWidthFrame(self.rotarFrame(self.framesc3d[num],matrices[i]))
            if(width>maxw):
                maxw=width
                besti=i
        self.estadisticas.append(abs((besti*5-90)+(self.getAngleOffset(num)*180/math.pi)))
        self.framesc3d[num]=self.rotarFrame(self.framesc3d[num],matrices[besti])
        self.frames[num]=self.rotarFrame(self.frames[num],matrices[besti])
    def getHeigthFrame(self,frame):
        minv=maxv=0
        for p in frame:
            if(p[2]<minv):
                minv=p[2]
            if(p[2]>maxv):
                maxv=p[2]
        return maxv-minv
    def getWidthFrame(self,frame):
        minv=maxv=0
        for p in frame:
            if(p[1]<minv):
                minv=p[1]
            if(p[1]>maxv):
                maxv=p[1]
        return maxv-minv
##        return (frame[16][1]-frame[9][1])
        
    def rotarFrame(self,frame,matrix):
        return np.dot(frame,matrix)
    def homologarPosicion(self):
        for i in range(len(self.frames)):
            self.centrarFrame(i)
    def centrarFrame(self,num):
        center=self.getCenterFrame(num)
        center[0]=-center[0]/2
        center[1]=-center[1]/2
        center[2]=-center[2]/2
        self.transladarFrame(num,center)
    def transladarFrame(self,num,vector):
        for p in self.framesc3d[num]:
            for i in range(0,len(p)):
                    p[i]+=vector[i]
        for p in self.frames[num]:
            for i in range(0,len(p)):
                    p[i]+=vector[i]

class CsvNormalizer(object):
    corners=[]#[i,j] where we change previous node of i so it becomes j
    #first element doesnt have previous so its fine whatever value of angle it has
    corners.append([4,2])
    corners.append([8,2])
    corners.append([12,0])
    corners.append([16,0])
    longitudes=[0,0.07,0.34,0.17,0.2,0.17,0.2,0.1,0.2,0.17,0.2,0.1,0.1,0.35,0.36,0.08,0.1,0.35,0.36,0.08]
    longitud=140##esta es la longitud "normal" de un "bone"
    ## un "bone" es la distancia entre un nodo y otro
    for i in range(len(longitudes)):
        longitudes[i]=longitudes[i]*longitud
    def getLengths(self,frame):
        lens=[]
        for i in range(1,len(frame)):
            ind=self.cornersIndex(i)
            if(ind==-1):
                ind=i-1
            v=0
            v+=(frame[i][0]-frame[ind][0])**2
            v+=(frame[i][1]-frame[ind][1])**2
            v+=(frame[i][2]-frame[ind][2])**2
            v=math.sqrt(v)
            v=float("{0:.2f}".format(v))
            lens.append(v)
        return lens
        
    def cornersIndex(self,i):
        for c in self.corners:
            if i == c[0]:
                return c[1]
        return -1
    def __init__(self):
        pass
    def normalizeAll(self,allframes):
        for i in range(len(allframes)):
            allframes[i]=self.normalize(allframes[i])
    def normalize(self,frame):
        angles=self.getAngles(frame)
        newframe=[]
        for i in range(len(frame)):
            if(i==0):
                newframe.append([0,0,0])
            else:
                p=self.longitudes[i]
                ind=self.cornersIndex(i)
                if(ind==-1):
                    ind=i-1
                x=newframe[ind][0]+(p*math.sin(angles[i][0])*math.cos(angles[i][1]))
                y=newframe[ind][1]+(p*math.sin(angles[i][0])*math.sin(angles[i][1]))
                z=newframe[ind][2]+(p*math.cos(angles[i][0]))
                newframe.append([x,y,z])
        return newframe
    def getAngles(self,frame):
        angles=[]
        for i in range(len(frame)):
            if(i==0):
                angles.append([0,0])
            else:
                ind=self.cornersIndex(i)
                if(ind==-1):
                    ind=i-1
                x=frame[i][0]-frame[ind][0]
                y=frame[i][1]-frame[ind][1]
                z=frame[i][2]-frame[ind][2]
                theta=math.acos(z/math.sqrt((x*x)+(y*y)+(z*z)))
                if(theta>math.pi):
                    theta-=math.pi
                else:
                    if(theta<0):
                        theta+=math.pi
                phi=math.atan2(y,x)
                if(phi>2*math.pi):
                    phi-=2*math.pi
                else:
                    if(phi<0):
                        phi+=2*math.pi
                angles.append([theta,phi])
        return angles
class CsvAnimation(Animation):
    scale=1
    frameRate=120
    initialrotation=0
    AntFramePosition=0
    ojospos=0
    csvnorm=0
    def toString(self):
        s=""
        for i in range(len(self.framesc3d)):
            s+=str(i)+" "
            for p in self.framesc3d[i]:
                for x in p:
                    s+="{0:.2f}".format(x)+" "
            s=s[:-1]
            s+="\n"
        s=s[:-1]
        return s        
    def mapearOjo(self,num):
        if len(self.ojospos)!=0:
            self.curves[num][0][0][1]+=self.ojospos[num][0]*self.Hradius
            self.curves[num][0][0][2]+=self.ojospos[num][1]*self.Hradius
    def mapearAllOjos(self):
        for i in range(len(self.curves)):
            self.mapearOjo(i)
    def centrarFrame(self,num):
        center=self.getCenterFrame(num)
        center[0]=-center[0]
        center[1]=-center[1]
        center[2]=-center[2]
        self.transladarFrame(num,center)
    def __init__(self,filename,onmarch,waits,val):
        self.csvnorm=CsvNormalizer()
        self.videolen=-1
        self.videoi=0
        self.videoframe=0
        self.ojospos=[]
        self.normh=50
        self.normw=50
        Animation.__init__(self,None,onmarch,waits,val)
        self.currenti=0
        self.matrices=[]
        self.toremove=[]
        self.curves=[]
        self.frames=[]
        self.framesc3d=[]
        self.strokesraw=[4,8,12,16,20]
        self.strokes=[2,4,8,12,15,19]
        self.tomerge=[]
        self.tomerge.append([14,1])
        self.tomerge.append([18,1])    
        
        self.filename=filename
        csvreader = csv.reader(open(filename,'r'), delimiter='\t')
        self.raw=[]
        i=-1
        ant=0
        fpsant=0
        promspf=0
        n=0
        if(onmarch):
            rawrows=[]
            for row in csvreader:
                if i==-1:
                    i=0
                    continue
                v=row[0].split(",")
                if(ant!=v[0]):
                    ant=v[0]
                    fpsant=int(v[2])
                    self.raw.append([])
                self.raw[len(self.raw)-1].append(row)
            self.preparar() 
        else:
            for row in csvreader:
                if i==-1:
                    i=0
                    continue
                v=row[0].split(",")
                if(ant!=v[0]):
                    ant=v[0]
                    if(not fpsant==0):
                        promspf+=abs(int(v[2])-fpsant)
                        n+=1
                    fpsant=int(v[2])
                    self.raw.append([])
                self.raw[len(self.raw)-1].append([float(v[8]),float(v[9]),float(v[10])])
            promspf/=n
            self.frameRate =1/(promspf*0.0001)
            
            self.procesar()
            self.simplify()
            self.decompose()
##            self.splineCurvas(waits,val)
            self.mapearAllOjos()
    def getHeigthFrame(self,frame):
        return math.sqrt((frame[1][0]-frame[2][0])**2+(frame[1][1]-frame[2][1])**2+(frame[1][2]-frame[2][2])**2)
    def getWidthFrame(self,frame):
        minv=maxv=0
        for p in frame:
            if(p[1]<minv):
                minv=p[1]
            if(p[1]>maxv):
                maxv=p[1]
        return maxv-minv
##        return (frame[8][1]-frame[4][1])
    def preparar(self):
        for i in range(-90,90,5):
            self.matrices.append(rotation_matrix([0,0,1],i*math.pi/180))
        self.initialrotation=rotation_matrix([1,0,0],math.pi/2)
        self.kineticGraph=GraphOnMarch()
        self.lagunaGraph=GraphOnMarch()
        for h in range(0,len(self.tomerge)):
            for g in range(1,self.tomerge[h][1]+1):
                self.toremove.append(self.tomerge[h][0]+g)
    def isAnimationFinished(self):
        return self.currenti>len(self.raw)-1
    def nextFrame(self):
        if self.isAnimationFinished():
            stop()
            return
        if(self.currenti==len(self.curves) and len(self.curves)!=len(self.raw)):
            rawframe=self.raw[self.currenti]
            self.procesarRawActual(rawframe)
            self.simplifyFrame(self.currenti)
            self.decomposeFrame(self.currenti)
            self.splineCurva(self.currenti,2,10)
            self.mapearOjo(self.currenti)
        self.dibujarFrame(self.slidei)
        self.dibujarCurva(self.currenti)
        self.dibujarVideo(self.currenti)
        self.dibujarProgreso()
    def getVideoFrame(self,num):
        q=float(num)/(len(self.raw)-1)
        q=min(int(q*self.videolen),self.videolen-1)
        if(self.videoi>q):
            self.video.release()
            self.video=cv2.VideoCapture(self.videostring)
            self.videoi=0
        
            image=self.video.read()
            image=image[1]
            im = Image.fromarray(image)
            im = ImageTk.PhotoImage(image=im)
            self.videoframe=im
            
            return self.getVideoFrame(num)
        if(self.videoi==q):
            return self.videoframe
        while self.videoi<q:
            image=self.video.read()
            self.videoi+=1
        image=image[1]
        im = Image.fromarray(image)
        im = ImageTk.PhotoImage(image=im)
        self.videoframe=im
        return self.videoframe
    def procesarRawActual(self,rawframe):
        frame=[]
        framec3d=[]
        v=rawframe[0][0].split(",")
        spf=(self.AntFramePosition-int(v[2]))*0.001
        if(spf<0):
            spf+=1
        self.AntFramePosition=int(v[2])
        for row in rawframe:
            v=row[0].split(",")
            frame.append([float(v[8]),float(v[9]),float(v[10])])
            framec3d.append([float(v[8]),float(v[9]),float(v[10])])
        self.frames.append(frame)
        self.framesc3d.append(framec3d) 

        self.centrarFrame(self.currenti)
        self.frames[self.currenti]=self.rotarFrame(self.frames[self.currenti][:],self.initialrotation)[:]
        self.framesc3d[self.currenti]=self.rotarFrame(self.framesc3d[self.currenti][:],self.initialrotation)[:]


##        self.corregirRotacionFrame(self.currenti,self.matrices)
        self.homologarEscalaFrame(self.currenti)
        
##        self.kineticGraph.addValue(kineticEnergy(self.framesc3d[self.currenti][:],self.framesc3d[self.currenti-1][:],spf))
##        self.lagunaGraph.addValue(kineticEnergy(self.framesc3d[self.currenti][:],self.framesc3d[0][:],spf))

        
    def simplifyFrame(self,num):
        frame=self.frames[num]
        for i in range(0,len(frame)):
            for h in range(0,len(self.tomerge)):
                if(i==self.tomerge[h][0]):
                    for g in range(1,self.tomerge[h][1]+1):
                        frame[i][0]+=frame[i+g][0]
                        frame[i][1]+=frame[i+g][1]
                        frame[i][2]+=frame[i+g][2]
                    frame[i][0]/=self.tomerge[h][1]+1
                    frame[i][1]/=self.tomerge[h][1]+1
                    frame[i][2]/=self.tomerge[h][1]+1
        newframe=[]
        for j in range(0,len(frame)):
            if (not(j in self.toremove)):
                newframe.append(frame[j])
        self.frames[num]=newframe
    def decomposeFrame(self,num):
        pi=0
        gi=0
        curveframe=[]
        curve=[]
        for p in self.frames[num]:
            curve.append(p)
            pi+=1
            if(gi<len(self.strokes) and pi==self.strokes[gi]):
                curveframe.append(curve[:])
                curve=[]
                gi+=1
        curveframe.append(curve[:])
        self.curves.append(curveframe)
        
        temp=self.curves[num][0][:]
        self.curves[num][0]=self.curves[num][1][:]
        self.curves[num][1]=temp

        self.curves[num][1].append(self.curves[num][0][0][:])
        del self.curves[num][0][0]

        self.curves[num].insert(0,[[self.curves[num][0][0][0],self.curves[num][0][0][1],self.curves[num][0][0][2]]])
##        self.curves[num].insert(0,self.curves[num][0][:])

        ##adding the neck point
        dx=self.curves[num][2][0][0]-self.curves[num][1][0][0]
        dy=self.curves[num][2][0][1]-self.curves[num][1][0][1]
        dz=self.curves[num][2][0][2]-self.curves[num][1][0][2]
        mv=math.sqrt(dx**2+dy**2+dz**2)
        t=self.Hradius/mv
        x=self.curves[num][1][0][0]+t*dx
        y=self.curves[num][1][0][1]+t*dy
        z=self.curves[num][1][0][2]+t*dz
        self.curves[num][2].append([x,y,z])

        ##adding joint points between arms and torso
        self.curves[num][3].insert(0,self.curves[num][2][len(self.curves[num][2])-2][:])
        self.curves[num][4].insert(0,self.curves[num][2][len(self.curves[num][2])-2][:])

        ##adding joint points between legs and torso
        self.curves[num][5].insert(0,self.curves[num][2][0][:])
        self.curves[num][6].insert(0,self.curves[num][2][0][:])
    def splineCurva(self,num,k=3,N=100):    
        for i in range(2,len(self.curves[num])):
            points = np.array(self.curves[num][i])
            self.curves[num][i]=BezierSpline(points,k,N)
    def getCenterFrame(self,num):
        return self.frames[num][0][:]
    def corregirLados(self):
        for num in range(len(self.frames)):
            if(self.frames[num][16][1]-self.frames[num][12][1]<0):
                matrix=rotation_matrix([0,0,1],math.pi)
                self.framesc3d[num]=self.rotarFrame(self.framesc3d[num],matrix)
                self.frames[num]=self.rotarFrame(self.frames[num],matrix)
    def ponerFrenteTodos(self):
        for i in range(len(self.frames)):
            self.ponerFrenteFrame(i)
    
    def procesar(self):
        frameAnt=0
        for fr in self.raw:
            frame=[]
            framec3d=[]
            for p in fr:
                vec=[p[0],p[1],p[2]]
                frame.append(vec)
                framec3d.append(vec[:])              
            self.frames.append(frame)
            self.framesc3d.append(framec3d)
        self.homologarPosicion()
        m=rotation_matrix([1,0,0],math.pi/2)
        for i in range(len(self.frames)):
            self.frames[i]=self.rotarFrame(self.frames[i],m)
            self.framesc3d[i]=self.rotarFrame(self.framesc3d[i],m)
        #N: 1.9226000309 T: 1.91519994736 el nuevo se demora 0.007400083544 segundos mas que el anterior
        #en promedio el nuevo se demora-0.326600027085segundos (midiendo a partir de 2 puntos arbitrarios)
##        self.ponerFrenteTodos()

        self.homologarEscala()
        
##        self.homologarRotacion()
        
        kineticdiff=[]
        lagunadiff=[]
        frameAnt=self.frames[0][:]
##        for i in range(1,len(self.framesc3d)):
##            if(i!=0):
##                kineticdiff.append(kineticEnergy(self.framesc3d[i][:],self.framesc3d[i-1][:],1/self.frameRate))
##                lagunadiff.append(kineticEnergy(self.framesc3d[i][:],self.framesc3d[0][:],1/self.frameRate))
        self.frames=np.array(self.frames)
        self.framesc3d=np.array(self.framesc3d)
    def eliminarAberrantes(self,lagunadiff,kineticdiff):
        aberranteslag=self.getIndicesAberrantes(lagunadiff,3)
        aberranteskin=self.getIndicesAberrantes(lagunadiff,3)
        aberrantes=dict([(a,1) for a in aberranteslag+aberranteskin]).keys()
        quickSort(aberrantes)
        aberrantes.reverse()
        for i in aberrantes:
            del self.frames[i]
            del self.framesc3d[i]
            del kineticdiff[i]
            del lagunadiff[i]
            del self.raw[i]
    def getIndicesAberrantes(self,data,criterio):
        indices=[]
        ordenados=data[:]
        quickSort(ordenados)
        q1=ordenados[int(len(ordenados)*0.25)]
        q3=ordenados[int(len(ordenados)*0.75)]
        RIQ=q3-q1
        for i in range(len(data)):
            if data[i]>(q3+criterio*RIQ):
                indices.append(i)
        return indices
    def homologarEscalaFrame(self,num):
        f=self.csvnorm.normalize(self.frames[num])
        self.frames[num]=f[:]
        self.framesc3d[num]=f
##        
##        frame=self.frames[num]
##        h=self.getHeigthFrame(frame)
##        w=math.sqrt(((frame[8][1]-frame[4][1])**2)+((frame[8][0]-frame[4][0])**2)+((frame[8][2]-frame[4][2])**2))
##        self.reescalarFrame(num,self.normh/h,self.normw/w)
    def homologarEscala(self):        
        for i in range(0,len(self.frames)):
            self.homologarEscalaFrame(i)
    def reescalarFrame(self,num,sch,scxy):
        for i in range(0,len(self.frames[num])):
            self.frames[num][i][0]*=scxy
            self.framesc3d[num][i][0]*=scxy
            self.frames[num][i][1]*=scxy
            self.framesc3d[num][i][1]*=scxy
            self.frames[num][i][2]*=sch
            self.framesc3d[num][i][2]*=sch
    def simplify(self):
        toremove=[]
        data=[]
        for h in range(0,len(self.tomerge)):
            for g in range(1,self.tomerge[h][1]+1):
                toremove.append(self.tomerge[h][0]+g)
        for frame in self.frames:
            for i in range(0,len(frame)):
                for h in range(0,len(self.tomerge)):
                    if(i==self.tomerge[h][0]):
                        for g in range(1,self.tomerge[h][1]+1):
                            frame[i][0]+=frame[i+g][0]
                            frame[i][1]+=frame[i+g][1]
                            frame[i][2]+=frame[i+g][2]
                        frame[i][0]/=self.tomerge[h][1]+1
                        frame[i][1]/=self.tomerge[h][1]+1
                        frame[i][2]/=self.tomerge[h][1]+1
        for frame in self.frames:
            newframe=[]
            for j in range(0,len(frame)):
                if (not(j in toremove)):
                    newframe.append(frame[j])
            data.append(newframe)
        self.frames=data
    def decompose(self):
        for i in range(len(self.frames)):
            self.decomposeFrame(i)
class EyeReader(object):
    upperDetector = cv2.CascadeClassifier("haarcascades\haarcascade_mcs_upperbody.xml")
    eyesDetector = cv2.CascadeClassifier("haarcascades\haarcascade_mcs_eyepair_small.xml")
    eyesDetector2 = cv2.CascadeClassifier("haarcascades\haarcascade_eye.xml")
    LearDetector = cv2.CascadeClassifier("haarcascades\haarcascade_mcs_rightear.xml")
    RearDetector = cv2.CascadeClassifier("haarcascades\haarcascade_mcs_leftear.xml")
    
    minSize=(150,150)
    eyes=0
    def __init__(self):
        self.eyes=[]
    def resizeTo(self,num):
        new=[]
        print(str(len(self.eyes)))
        for i in range(num):
            new.append(self.eyes[min(int((float(i)/num)*len(self.eyes)),len(self.eyes)-1)])
        return new
    def getEyes(self,frame):
        result=0
        frameGray = cv2.cvtColor(frame, cv2.COLOR_BGR2GRAY)
        head = self.upperDetector.detectMultiScale(frameGray, scaleFactor=1.3,minSize=self.minSize, minNeighbors=4)
        if(len(head)>0):
            ux=head[0][0]
            uy=head[0][1]
            uw=head[0][2]
            uh=head[0][3]
            hw = hh = int(round(uw*0.4333))#era 0.5333
            hx = ux + int((uw-hw)/2)
            hy = uy + (uh-hh)/5
            roiHead = frameGray[hy:hy+hh , hx:hx+hw]        
            roiHead = cv2.resize(roiHead,self.minSize)
            roiHead = cv2.equalizeHist(roiHead)
            roiHead = cv2.blur(roiHead, (3,3)) 
            
            minX = roiHead.shape[0]/3
            maxX = roiHead.shape[0]/2
            minY = roiHead.shape[0]/15
            maxY = roiHead.shape[0]/7

            #Detector de par de ojos
            eyes = self.eyesDetector.detectMultiScale(roiHead, minNeighbors=4, minSize=(minX,minY), maxSize=(maxX,maxY))
            #Si set detecta el par de ojos
            fw=float(hw)/self.minSize[0]
            fh=float(hh)/self.minSize[1]
            if(eyes != ()):
                ex,ey,ew,eh = eyes[0]
                result=[int((ex)*fw),int((ey)*fh)]
                result[0]+=((ew)*fw)/2
                result[1]+=((eh)*fh)/2
            else:
                minS = roiHead.shape[0]/8
                maxS = roiHead.shape[0]/6
                eyes = self.eyesDetector2.detectMultiScale(roiHead, minNeighbors=10, minSize=(minS,minS), maxSize=(maxS,maxS))
                if(eyes != ()):
                    if(len(eyes)>1):
                        x1,y1,w1,h1 = eyes[0]
                        x2,y2,w2,h2 = eyes[1]
                        ex=x1
                        ey=y1
                        ew=(x2-x1+w2)
                        eh=(y2-y1+h2)
                        result=[int((ex)*fw),int((ey)*fh)]
                        result[0]+=((ew)*fw)/2
                        result[1]+=((eh)*fh)/2
                        
                    else:
                        ex,ey,ew,eh = eyes[0]
                        result=[int((ex)*fw),int((ey)*fh)]
                        result[0]+=((ew)*fw)/2
                        result[1]+=((eh)*fh)/2
                else:
                    Lear = self.LearDetector.detectMultiScale(roiHead)
                    if(Lear != ()):
                        result=[0.0,0.5]
                    else:
                        Rear = self.RearDetector.detectMultiScale(roiHead)
                        if(Rear != ()):
                            result=[1.0,0.5]
        if(result!=0):
            result[0]=float(result[0])/hw
            result[1]=float(result[1])/hh
            result[0]=result[0]-0.5
            result[1]=result[1]-0.5
        return result
    def rellenarTodo(self):
        foco=True
        while(foco):
            foco=self.rellenarHueco()
    def rellenar(self,hueco):
        x=np.linspace(self.eyes[hueco[0]-1][0],self.eyes[hueco[1]+1][0],hueco[1]-hueco[0]+1)
        y=np.linspace(self.eyes[hueco[0]-1][1],self.eyes[hueco[1]+1][1],hueco[1]-hueco[0]+1)
        for i in range(hueco[0],hueco[1]+1):
            self.eyes[i]=[x[i-hueco[0]],y[i-hueco[0]]]
    def rellenarHueco(self):
        hueco=[-1,-1]
        if(self.eyes[0]==0):
            self.eyes[0]=[0.0,0.0]
            return True
        if(self.eyes[len(self.eyes)-1]==0):
            self.eyes[len(self.eyes)-1]=[0.0,0.0]
            return True
        for i in range(len(self.eyes)):
            if self.eyes[i]==0 and hueco[0]==-1:
                hueco[0]=i
            if hueco[0]!=-1 and self.eyes[i]!=0:
                hueco[1]=i-1
                self.rellenar(hueco)
                return True
        return False
def new_mainloop():
##    while(not isdone):
##        master.update()
##    afterinit()
    global tasks
    while(True):
        master.update()
        if(len(tasks)!=0):
            for t in tasks:
                t()
            tasks=[]
    master.destroy()
def rotation_matrix(axis, theta):
    axis = np.asarray(axis)
    theta = np.asarray(theta)
    axis = axis/math.sqrt(np.dot(axis, axis))
    a = math.cos(theta/2)
    b, c, d = -axis*math.sin(theta/2)
    aa, bb, cc, dd = a*a, b*b, c*c, d*d
    bc, ad, ac, ab, bd, cd = b*c, a*d, a*c, a*b, b*d, c*d
    return np.array([[aa+bb-cc-dd, 2*(bc+ad), 2*(bd-ac)],
                     [2*(bc-ad), aa+cc-bb-dd, 2*(cd+ab)],
                     [2*(bd+ac), 2*(cd-ab), aa+dd-bb-cc]])
def scaling_matrix(vx,vy,vz):
    return np.array([[vx,0,0],
                     [0,vy,0],
                     [0,0,vz]])
def drawLines(pt,color):
    global primera
    if primera==0:
        primera=pt
    else:
        w.create_line(primera[0],primera[1],pt[0],pt[1],fill =color ,width=3)
        primera=pt
        
def drawLinesSlide(pt,color):
    global primera
    if primera==0:
        primera=pt
    else:
        wslide.create_line(primera[0],primera[1],pt[0],pt[1],fill =color ,width=3)
        primera=pt

def drawOvalsPlayer(pt,color):
    w.create_oval(pt[0]-5,pt[1]-5,pt[0]+5,pt[1]+5,fill=color)
def drawOvals(pt,color):
    wslide.create_oval(pt[0]-5,pt[1]-5,pt[0]+5,pt[1]+5,fill=color)
def drawEmptyOval(pt,rad,color):
    w.create_oval(pt[0]-rad,pt[1]-rad,pt[0]+rad,pt[1]+rad,outline=color,width=3)
  
def openCallBack():
    filename = askopenfilename(parent=master)
    loadAnimationWScreen(filename)
def loadAnimationWScreen(s):
    w=WaitScreen("cargando animación")
    w.start(lambda string=s,waits=w:loadAnimation(string,waits))
def loadAnimation(string,waits):
    ends=[]
    waits.avanzar(0,"creando la animacion")
    head, tail = ntpath.split(string)
    vs=string[:-4]
    ext=tail[-4:]
    tail=tail[:-4]
    if(string==""):
        waits.terminar()
        return
    ends.append(70.0)
    if(ext==".c3d"):
        ends.append(1.0)
    else:
        ends.append(30.0)
    n=0
    for i in range(len(ends)):
        n+=ends[i]
    for i in range(len(ends)):
        ends[i]/=n
    video = cv2.VideoCapture(vs+".avi")
    anim=0
    visionReader=0
    if(ext==".c3d"):
        anim=Animation(string,False,waits,ends[0])
    else:
        anim=CsvAnimation(string,False,waits,ends[0])
    visionReader=EyeReader()
    anim.videostring=vs+".avi"
    anim.video=cv2.VideoCapture(anim.videostring)
    success=True    
    if(int(video.get(5))!=0):
        anim.frameRate=int(video.get(5))
    anim.videolen=int(video.get(cv2.cv.CV_CAP_PROP_FRAME_COUNT))
    waits.avanzar(1,"leyendo las posiciones de los ojos")
    while(success):
        success,image=video.read()
        if(not success):
            break
        if visionReader!=0:
            visionReader.eyes.append(visionReader.getEyes(image))
        waits.avanzar(ends[1]*100/anim.videolen,"leyendo las posiciones de los ojos")
    waits.avanzar(0,"añadiendo animacion al espacio de trabajo")
    if visionReader!=0 and anim.videolen!=0:
        visionReader.rellenarTodo()
        anim.ojospos=visionReader.resizeTo(len(anim.raw))
    global animation
    animation=anim
    setAnimation(animation)
    video.release()
    waits.terminar()
def setAnimation(anim):
    global fetcher
    global vision
    global draw
    vision.setAnimation(anim)
    fetcher.setAnimation(anim)
    draw.bottomButton.config(state=NORMAL)
def bspline3D(d,K,N):
    x=bsplineAnt(d[:,0],K,N)
    y=bsplineAnt(d[:,1],K,N)
    z=bsplineAnt(d[:,2],K,N)
    nuevo=[]
    for j in range(0,len(x)):
        nuevo.append([x[j],y[j],z[j]])
    return nuevo
def bsplineAnt(d, K=3, N=100):
    K=min(len(d)-1,K)
    t = range(len(d))
    ipl_t = np.linspace(0.0, len(d) - 1, N)
    x_tup = si.splrep(t, d, k=K)
    x_list = list(x_tup)
    xl = d.tolist()
    x_list[1] = xl + [0.0, 0.0, 0.0, 0.0]
    x_i = si.splev(ipl_t, x_list)
    return x_i
#http://devosaurus.blogspot.com/2013/10/exploring-b-splines-in-python.html  
def make_knot_vector(n, m):
    total_knots = m+n+2                           
    outer_knots = n+1                            
    inner_knots = total_knots - 2*(outer_knots)
    knots  = [0]*(outer_knots)
    knots += [i for i in range(1, inner_knots)]
    knots += [inner_knots]*(outer_knots)
    return tuple(knots) 
def C_factory(P, V=None, n=2):
    m = len(P)    
    D = len(P[0]) 
    b_n = basis_factory(n)
    def S(t, d):
        out=0.
        for i in range(m):
            out += P[i][d]*b_n(t, i, V)
        return out
    def C(t):
        out = [0.]*D           
        for d in range(D):     
            out[d] = S(t,d)
        return out   
    C.V = V                   
    C.spline = S              
    C.basis = b_n             
    C.min = V[0]              
    C.max = V[-1]-0.0001             
    C.endpoint = True#C.max!=V[-1]
    return C
def basis_factory(degree):
    if degree == 0:
        def basis_function(t, i, knots):
            t_this = knots[i]
            t_next = knots[i+1]
            out = 1. if (t>=t_this and t< t_next) else 0.         
            return out
    else:
        def basis_function(t, i, knots):
            out = 0.
            t_this = knots[i]
            t_next = knots[i+1]
            t_precog  = knots[i+degree]
            t_horizon = knots[i+degree+1]            
            top = (t-t_this)
            bottom = (t_precog-t_this)
            if bottom != 0:
                out  = top/bottom * basis_factory(degree-1)(t, i, knots)
                
            top = (t_horizon-t)
            bottom = (t_horizon-t_next)
            if bottom != 0:
                out += top/bottom * basis_factory(degree-1)(t, i+1, knots)
            return out       
    basis_function.lower = None if degree==0 else basis_factory(degree-1)
    basis_function.degree = degree
    return basis_function
def BezierSpline(d,K,N):
    n = K
    V = make_knot_vector(n, len(d))
    C = C_factory(d, V, n)
    sampling = [t for t in np.linspace(C.min, C.max, N,endpoint=C.endpoint)]
    curvepts = [ C(s) for s in sampling ]
    return curvepts
def play():
    if len(animframe.animations)==0:
        return
    if(animframe.getAnim().isAnimationFinished()):
        progress["value"] = 0
        animframe.getAnim().currenti=0
    global playing
    playing=True
    play_pause.config(image=pausegif,width="20",height="20",command = pause)
def pause():
    if len(animframe.animations)==0:
        return
    global playing
    playing=False
    play_pause.config(image=playgif,width="20",height="20",command = play)
def setFrame(event):
    if len(animframe.animations)==0:
        return
    framei=int(len(animframe.getAnim().frames)*(float(event.x)/progress.winfo_width()))
    framei=max(min(framei,len(animframe.getAnim().frames)-1),0)
    animframe.getAnim().currenti=framei
    progress["value"]=animframe.getAnim().currenti
global master
master = Tk()
master.columnconfigure(0, weight=1)
master.columnconfigure(1, weight=1)
master.rowconfigure(1, weight=1)
##master.grid_propagate(False)
def clickFrame(event):
    global fetcher
    global vision
    i=int(fetcher.canvas.canvasx(event.x)/fetcher.gifwidth)
    vision.dibujar(i)
    fetcher.selectFrame(i)
class FetcherFrame(Frame):
    canvas=0
    posegif=0
    poseSgif=0
    gifwidth=0
    gifheight=0
    hbar=0
    Nframes=0
    image=0
    niveles=0
    mapbar=0
    def __init__(self,master):
        Frame.__init__(self,master,relief=FLAT)
        self.config(height=30)
        self.grid(column=0,row=0,columnspan=2,sticky=W+E)
        self.canvas=Canvas(self,height=30)
        self.canvas.pack(expand=1,fill=BOTH)
        self.posegif = PhotoImage(file='frame.gif')
        self.poseSgif = PhotoImage(file='frameS.gif')
        self.canvas.bind("<Button-1>", clickFrame)
        self.gifwidth=self.posegif.width()
        self.gifheight=self.posegif.height()
        self.hbar=Scrollbar(self,orient=HORIZONTAL)
        self.hbar.pack(side=BOTTOM,fill=X)
        self.hbar.config(command=self.canvas.xview)
        self.canvas.config(xscrollcommand=self.hbar.set)
        self.mapbar=Canvas(self,height=4)
        self.mapbar.pack(expand=1,side=BOTTOM,fill=X)
        self.canvas.bind("<Configure>",self.dibujarMap)
        self.niveles=[]
        
    def assignLevels(self,levels=[]):
        self.niveles=[]
        if(len(levels)==0):
            self.niveles=[0.0]*self.Nframes
        else:
            self.niveles=np.array(levels)
            maxv=max(self.niveles)
            minv=min(self.niveles)
            self.niveles=np.divide(np.subtract(self.niveles,[minv]*len(self.niveles)),([maxv-minv]*len(self.niveles)))
            self.selectFrame(-1)
            self.dibujarMap(0)   
    def dibujarMap(self,evt):
        if self.Nframes<=0:
            return
        offset=17
        self.mapbar.delete("all")
        wid=self.mapbar.winfo_width()-offset*2
        he=self.mapbar.winfo_height()
        for i in range(wid):
            v=int(255 * self.niveles[int((float(i)/wid)*len(self.niveles))])
            color='#%02x%02x%02x'%(v,v,v)
            self.mapbar.create_line(offset+i,0,offset+i,he, fill=color)
    def setAnimation(self,anim):
        self.canvas.delete("all")
        self.Nframes=len(anim.frames)
        self.canvas.config(scrollregion=(0,0,self.gifwidth*self.Nframes,0))
        self.assignLevels()
        for i in range(self.Nframes):
            self.canvas.create_image((i+0.5)*self.gifwidth,self.gifheight/2, image=self.posegif)
        self.update()
        self.update_idletasks()
    def selectFrame(self,iS):
        self.canvas.delete("all")
        for i in range(self.Nframes):
            if i!=iS:
                self.canvas.create_image((i+0.5)*self.gifwidth,self.gifheight/2, image=self.posegif)
            else:
                self.canvas.create_image((i+0.5)*self.gifwidth,self.gifheight/2, image=self.poseSgif)
            self.canvas.create_rectangle(i*self.gifwidth,int((1-self.niveles[i])*self.gifheight),(i+1)*self.gifwidth,self.gifheight, fill="green")
class DrawFrame(Frame):
    canvas=0
    strokes=0
    currentpoints=0
    bottomButton=0
    buttonraw=0
    buttonnormal=0
    buttonsmooth=0
    buttonedit=0
    rawgif=0
    normalgif=0
    smoothgif=0
    editgif=0
    splined=0
    body=0
    stickfigure=0
    buttonframe=0
    head=0
    cargargif=0
    guardargif=0
    cargarbut=0
    guardarbut=0
    def __init__(self,master):
        Frame.__init__(self,master,bd=3,relief=RIDGE)
        self.grid(column=0,row=1,sticky=W+E+N+S)
        self.canvas=Canvas(self)
        self.canvas.pack(expand=1,fill=BOTH)
        self.currentpoints=[]
        self.strokes=[]
        self.splined=[]
        self.stickfigure=[]
        self.head=[]
        self.canvas.bind( "<B1-Motion>", paintDraw )
        self.canvas.bind( "<Button-1>", clickedDraw )
        self.canvas.bind( "<ButtonRelease-1>", releaseDraw )
        self.canvas.bind( "<Button-3>", clicked3Draw )
        self.config(cursor="pencil")
        self.bottomButton=Button(self.canvas,text="Hecho!",command=self.hechoAction,state=DISABLED)
        self.bottomButton.pack(side=BOTTOM)
        self.bottomButton.config(cursor="arrow")
        self.rawgif=PhotoImage(file="raw.gif")
        self.normalgif=PhotoImage(file="normal.gif")
        self.smoothgif=PhotoImage(file="smooth.gif")
        self.editgif=PhotoImage(file="editar.gif")
        self.cargargif=PhotoImage(file="cargar.gif")
        self.guardargif=PhotoImage(file="guardar.gif")
        self.buttonframe=Frame(self.canvas)
        self.buttonframeleft=Frame(self.canvas)
        self.cargarbut=Button(self.buttonframeleft,image=self.cargargif,command=self.cargarAction,cursor="arrow")
        self.guardarbut=Button(self.buttonframeleft,image=self.guardargif,command=self.guardarAction,cursor="arrow")
        self.cargarbut.pack(side=TOP)
        self.guardarbut.pack(side=TOP)
        self.buttonframeleft.pack(side=LEFT)
        self.buttonraw=Button(self.buttonframe,image=self.rawgif,command=self.rawAction)
        self.buttonraw.pack(side=TOP)
        self.buttonnormal=Button(self.buttonframe,image=self.normalgif,command=self.normalAction)
        self.buttonnormal.pack(side=TOP)
        self.buttonsmooth=Button(self.buttonframe,image=self.smoothgif,command=self.smoothAction)
        self.buttonsmooth.pack(side=TOP)
        self.buttonedit=Button(self.buttonframe,image=self.editgif,command=self.editAction)
        self.buttonedit.pack(side=TOP)
    def guardarAction(self):
        global master
        filename = asksaveasfilename(parent=master)
        if filename=='':
            return
        filename = open(filename, 'w')
        for s in self.strokes:
            for p in s:
                for v in p:
                    filename.write(str(v))
                    filename.write(",")
                filename.write("@")
            filename.write("#")
        filename.close()
    def cargarAction(self):
        global master               
        filename = askopenfilename(parent=master)
        if filename=='':
            return
        filename = open(filename, 'r')
        string=filename.read()
        string=string.split("#")[:-1]
        self.strokes=[]
        for s in string:
            newstroke=[]
            for p in s.split("@")[:-1]:
                newp=[]
                for v in p.split(",")[:-1]:
                    newp.append(float(v))
                newstroke.append(newp)
            self.strokes.append(newstroke)
        self.canvas.delete("all")
        self.drawAllNormal(self.strokes,"blue")
        if(self["relief"]==RAISED):
            self.hechoAction()
    def rawAction(self):
        if(self.buttonraw["relief"]==RAISED):
            self.buttonraw.config(relief=SUNKEN)
            self.buttonnormal.config(relief=RAISED)
            self.buttonsmooth.config(relief=RAISED)
            self.bottomButton.config(state = NORMAL,command=self.compararStick)
            self.canvas.delete("all")
            self.drawAllRaw(self.stickfigure)
    def normalAction(self):
        if(self.buttonnormal["relief"]==RAISED):
            self.buttonnormal.config(relief=SUNKEN)
            self.buttonsmooth.config(relief=RAISED)
            self.buttonraw.config(relief=RAISED)
            self.bottomButton.config(state = DISABLED)
            self.canvas.delete("all")
            self.drawAllNormal(self.strokes,"blue")
    def smoothAction(self):
        if(self.buttonsmooth["relief"]==RAISED):
            self.buttonsmooth.config(relief=SUNKEN)
            self.buttonnormal.config(relief=RAISED)
            self.buttonraw.config(relief=RAISED)
            self.bottomButton.config(state = NORMAL,command=self.compararSpline)
            self.canvas.delete("all")
            self.drawAllSmooth(self.splined,"red")
    def isHuman(self):
        return len(self.strokes)==6
    def hechoAction(self):
        if not self.isHuman():
            tkMessageBox.showinfo("No es humano", "El stickfigure que dibujó no es de un humano\nverifique que haya hecho un trazo por cada parte del cuerpo y vuelva a intentarlo")
            return
        self.bottomButton.config(text="Comparar",command=self.compararSpline,state=DISABLED)
        self.config(relief=RAISED)
        self.canvas.unbind("<B1-Motion>")
        self.canvas.unbind("<Button-1>")
        self.canvas.unbind("<ButtonRelease-1>")
        self.canvas.unbind("<Button-3>")
        self.config(cursor="arrow")
        
        self.buttonnormal.config(relief=SUNKEN)
        self.buttonraw.config(relief=RAISED)
        self.buttonsmooth.config(relief=RAISED)
        self.buttonframe.pack(side=RIGHT)

        ir=getRoundest(self.strokes)
        rad=getRadius(self.strokes[ir])
        head=getCircle(rad,250)
        c=Centroid(self.strokes[ir])
        offset(head,c)
        self.head=head
        
        self.body=[]
        for i in range(len(self.strokes)):
            if i!=ir:
                self.body.append(self.strokes[i][:])
        self.ordenarBody()
        self.body[0].append(c)
        self.stickfigure=toStick(self.body)
        self.completeBody()
        self.arreglarCuello(c,rad)
        self.splined=toSpline(self.body)
    def estaDentroCabeza(self,p,c,rad):
        return Distance(p,c)<=rad
    def arreglarCuello(self,c,rad):
        while(self.estaDentroCabeza(self.body[0][-1],c,rad)):
            self.body[0]=self.body[0][:-1]
        start=self.body[0][-1]
        end=c
        delta=[end[0]-start[0],end[1]-start[1]]
        p=1-(float(rad)/Distance(start,end))
        end=[start[0]+p*delta[0],start[1]+p*delta[1]]
        self.body[0].append(end)
    def compararSpline(self):
        start=time.time()
        global fetcher
        global vision
        scale=100
        stick=self.splined[:]
        for i in range(len(stick)):
            stick[i]=TranslateTo(stick[i],[0,0])
            stick[i]=ScaleTo(stick[i],scale)
##            v=getAngles2D(stick[i])##comentar para comparar con las posiciones
##            stick[i]=v
        levels=[]
        for i in range(fetcher.Nframes):
            error=0
            frame=vision.anim.getCurva2D(i)
            for i in range(len(frame)):
                frame[i]=TranslateTo(frame[i],[0,0])
                frame[i]=ScaleTo(frame[i],scale)
##                angles=getAngles2D(frame[i])##comentar para comparar con las posiciones
##                error+=np.sum(np.absolute(np.subtract(angles,stick[i])))
                error+=compareStrokes(frame[i],stick[i])
##                error+=compareAngles2D(frame[i],stick[i])
            error/=len(frame)
            levels.append(1/error)
        fetcher.assignLevels(levels)
        end=time.time()
        print("se demoro "+str(end-start)+"segundos")
        index=fetcher.niveles.argmax()
        vision.dibujar(index)
        fetcher.selectFrame(index)
        fetcher.canvas.xview(MOVETO,float(index-float(fetcher.canvas.winfo_width())/(2*fetcher.gifwidth))/fetcher.Nframes)
    def compararStick(self):
        start=time.time()
        global fetcher
        global vision
        scale=100
        stick=self.stickfigure[:]
        for i in range(len(stick)):
            stick[i]=TranslateTo(stick[i],[0,0])
            stick[i]=ScaleTo(stick[i],scale)
##            stick[i]=getAngles2D(stick[i])##comentar para comparar con las posiciones
        levels=[]
        for i in range(fetcher.Nframes):
            error=0
            frame=separar(vision.anim.getFrame2D(i))
            for i in range(len(frame)):
                error+=compareAngles2D(frame[i],stick[i])
                frame[i]=TranslateTo(frame[i],[0,0])
                frame[i]=ScaleTo(frame[i],scale)
##                frame[i]=getAngles2D(frame[i])##comentar para comparar con las posiciones
##                error+=np.sum(np.absolute(np.subtract(frame[i],stick[i])))
                error+=compareStrokes(frame[i],stick[i])
            error/=len(frame)
            levels.append(1/error)
        fetcher.assignLevels(levels)
        end=time.time()
        print("se demoro "+str(end-start)+"segundos")
        index=fetcher.niveles.argmax()
        vision.dibujar(index)
        fetcher.selectFrame(index)
        fetcher.canvas.xview(MOVETO,float(index-float(fetcher.canvas.winfo_width())/(2*fetcher.gifwidth))/fetcher.Nframes)
    def editAction(self):
        self.bottomButton.config(text="Hecho!",command=self.hechoAction)
        self.config(relief=RIDGE)
        self.canvas.bind( "<B1-Motion>", paintDraw )
        self.canvas.bind( "<Button-1>", clickedDraw )
        self.canvas.bind( "<ButtonRelease-1>", releaseDraw )
        self.canvas.bind( "<Button-3>", clicked3Draw )
        self.config(cursor="pencil")
        self.bottomButton.config(state = NORMAL)
        self.buttonframe.pack_forget()
        self.splined=[]
        self.stickfigure=[]
        self.canvas.delete("all")
        self.drawAllNormal(self.strokes,"blue")
    def drawAllNormal(self,All,color):
        for a in All:
            self.drawPoints(a,color)
    def drawAllSmooth(self,All,color):
        for a in All:
            self.drawPoints(a,color)
        self.drawPoints(self.head,color)
    def drawAllRaw(self,All):
        colors=["blue","green","red","black","yellow"]
        for i in range(len(All)):
            self.drawPointsStick(All[i],colors[i])
        self.drawPoints(self.head,"magenta")
    def drawPoints(self,todraw,color):
        primera=0
        for a in todraw:
            if primera==0:
                primera=a
            else:
                self.canvas.create_line(primera[0],primera[1],a[0],a[1],fill = color,width=7)
                primera=a
    def drawPointsStick(self,todraw,color):
        primera=0
        for a in todraw:
            if primera==0:
                primera=a
            else:
                self.canvas.create_line(primera[0],primera[1],a[0],a[1],fill = color,width=2)
                primera=a
            self.canvas.create_oval(a[0]-2.5,a[1]-2.5,a[0]+2.5,a[1]+2.5,fill="red")
        self.canvas.create_oval(todraw[0][0]-2.5,todraw[0][1]-2.5,todraw[0][0]+2.5,todraw[0][1]+2.5,fill="blue")
        self.canvas.create_oval(todraw[len(todraw)-1][0]-2.5,todraw[len(todraw)-1][1]-2.5,todraw[len(todraw)-1][0]+2.5,todraw[len(todraw)-1][1]+2.5,fill="orange")
    def completeBody(self):
        centerarms=[(self.body[1][0][0]+self.body[2][0][0])/2,(self.body[1][0][1]+self.body[2][0][1])/2]
        self.body[1].insert(0,centerarms[:])
        self.body[2].insert(0,centerarms[:])
        self.body[3].insert(0,self.body[0][0][:])
        self.body[4].insert(0,self.body[0][0][:])
        
    def ordenarBody(self):
        self.centers=[]
        for i in range(len(self.body)):
##            self.centers.append(self.body[i][int(len(self.body[i])/2)])
            self.centers.append(Centroid(self.body[i]))
        ti=getTorso(self.body)

        self.body.insert(0, self.body.pop(ti))
        self.centers.insert(0, self.centers.pop(ti))

        arm=-1
        d=99999999
        for i in range(1,len(self.centers)):
            if(self.centers[i][1]<d):
                d=self.centers[i][1]
                arm=i
        
        self.body.insert(1, self.body.pop(arm))
        self.centers.insert(1, self.centers.pop(arm))

        arm=-1
        d=99999999
        for i in range(2,len(self.centers)):
            if(self.centers[i][1]<d):
                d=self.centers[i][1]
                arm=i
        
        self.body.insert(2, self.body.pop(arm))
        self.centers.insert(2, self.centers.pop(arm))

        if self.body[0][0][1]<self.body[0][len(self.body[0])-1][1]:
            self.body[0]=self.body[0][::-1]
            
        self.ordenarBrazos()
        self.ordenarPiernas()
    def ordenarBrazos(self):
        if(self.centers[1][0]>self.centers[2][0]):
            self.centers[1],self.centers[2]=self.centers[2],self.centers[1]
            self.body[1],self.body[2]=self.body[2],self.body[1]
        dmin=9999999
        change=[False,False]
        d=Distance(self.body[1][0],self.body[0][int(len(self.body[0])*0.75)])
        d2=Distance(self.body[1][len(self.body[1])-1],self.body[0][int(len(self.body[0])*0.75)])
        if(d2<d):
            change[0]=True

        d=Distance(self.body[2][0],self.body[0][int(len(self.body[0])*0.75)])
        d2=Distance(self.body[2][len(self.body[2])-1],self.body[0][int(len(self.body[0])*0.75)])
        if(d2<d):
            change[0]=True
            
##        d=Distance(self.body[1][0],self.body[2][0])
##        if(d<dmin):
##            dmin=d
##            change=[False,False]
##        d=Distance(self.body[1][len(self.body[1])-1],self.body[2][0])
##        if(d<dmin):
##            dmin=d
##            change=[True,False]
##        d=Distance(self.body[1][0],self.body[2][len(self.body[2])-1])
##        if(d<dmin):
##            dmin=d
##            change=[False,True]
##        d=Distance(self.body[1][len(self.body[1])-1],self.body[2][len(self.body[2])-1])
##        if(d<dmin):
##            dmin=d
##            change=[True,True]
            
        if change[0]:
            self.body[1]=self.body[1][::-1]
        if change[1]:
            self.body[2]=self.body[2][::-1]
        
    def ordenarPiernas(self):
        if(self.centers[3][0]>self.centers[4][0]):
            self.centers[3],self.centers[4]=self.centers[4],self.centers[3]
            self.body[3],self.body[4]=self.body[4],self.body[3]

        if self.body[3][0][1]>self.body[3][len(self.body[3])-1][1]:
            self.body[3]=self.body[3][::-1]
        if self.body[4][0][1]>self.body[4][len(self.body[4])-1][1]:
            self.body[4]=self.body[4][::-1]
def cornersIndex(corners,i):
        for c in corners:
            if i == c[0]:
                return c[1]
        return -1

def getAngles2D(frame):
    angles=[]
    for i in range(1,len(frame)):
            ind=i-1
            x=frame[i][0]-frame[ind][0]
            y=frame[i][1]-frame[ind][1]
            theta=math.atan2(y,x)
            angles.append(theta)
    return np.array(angles)
def compareAngles2D(frameA,frameB):
    error=[]
    for i in range(1,len(frameA)):
            ind=i-1
            x1=frameA[i][0]-frameA[ind][0]
            y1=frameA[i][1]-frameA[ind][1]
            x2=frameB[i][0]-frameB[ind][0]
            y2=frameB[i][1]-frameB[ind][1]
            dot = x1*x2 + y1*y2
            det = x1*y2 - y1*x2
            theta=math.atan2(det,dot)
            error.append(theta)
    return abs(np.sum(np.array(error))/len(error))

def combinar(trazos):
    combinados=[]
    for i in range(len(trazos)):
        for j in range(len(trazos[i])):
            combinados.append(trazos[i][j])            
    return np.array(combinados)
def separar(combinados):
    separados=[]
    separados.append(combinados[:4])
    separados.append(combinados[4:8])
    separados.append(combinados[8:12])
    separados.append(combinados[12:16])
    separados.append(combinados[16:])
    return separados
def TranslateTo(pts,p):
   c=Centroid(pts)
   return np.subtract(np.add(pts,[p]*len(pts)),[c]*len(pts))
def getInclinacion(stroke):
    c=Centroid(stroke)
    v=0
    for p in stroke:
       v+=(p[0]-c[0])**2
    v/=len(stroke)
    return v
def getTorso(body):
    maxy=0
    eliminar=-1
    ignorar=[]
    for i in range(len(body)):
        y=Centroid(body[i])[1]
        if y> maxy:
            maxy=y
            eliminar=i
    ignorar.append(eliminar)
    miny=999999999
    eliminar=-1
    for i in range(len(body)):
        y=Centroid(body[i])[1]
        if y>maxy and not(i in ignorar):
            maxy=y
            eliminar=i
    ignorar.append(eliminar)
    res=-1
    for i in range(len(body)):
        inc=getInclinacion(body[i])
        if y< miny and not(i in ignorar):
            miny=y
            res=i
    return res
    
##    minp=[9999999,999999]
##    maxp=[0,0]
##    for s in body:
##        for p in s:
##            minp[0]=min(p[0],minp[0])
##            minp[1]=min(p[1],minp[1])
##            maxp[0]=max(p[0],maxp[0])
##            maxp[1]=max(p[1],maxp[1])
##    for c in centers:
##        minp[0]=min(c[0],minp[0])
##        minp[1]=min(c[1],minp[1])
##        maxp[0]=max(c[0],maxp[0])
##        maxp[1]=max(c[1],maxp[1])
##    center=[(minp[0]+maxp[0])/2,(minp[1]+maxp[1])/2]
##    distance=9999999
##    res=-1
##    for i in range(len(body)):
##        d=0
##        for p in body[i]:
##            d+=Distance(p,center)
##        if d<distance:
##            distance=d
##            res=i
##    return res
##    for i in range(len(centers)):
##        d=Distance(centers[i],center)
##        if(d<distance):
##            distance=d
##            res=i
##    return res
def PathLength(pts):
   d = 0
   primera=0
   for a in pts:
          if primera==0:
             primera=a
          else:
             d+=Distance(primera,a)
             primera=a
   return d
def ordenarStroke(stroke):
    if(stroke[0][1]>stroke[len(stroke)-1][1]):
        return stroke[:]
    else:
        return list(reversed(stroke))
def toSpline(points):
    newpoints=[]
    global vision
    curva=vision.anim.getCurva2D(0)
    for i in range(len(points)):
        newpoints.append(BezierSpline(points[i],2,len(curva[i])))
    return newpoints
def toStick(points):
    newpoints=[]
    for i in range(0,len(points)):
        newpoints.append(BezierSpline(points[i],2,4))
    return newpoints
def paintDraw(event):
    global draw
    draw.canvas.create_line(draw.currentpoints[len(draw.currentpoints)-1][0],draw.currentpoints[len(draw.currentpoints)-1][1],event.x,event.y,fill = "blue",width=7)
    draw.currentpoints.append([event.x,event.y])
def clickedDraw(event):
    global draw
    draw.currentpoints=[]
    draw.currentpoints.append([event.x,event.y])
def offset(points,p):
    for i in range(len(points)):
        for j in range(len(points[i])):
            points[i][j]+=p[j]
def Distance(p1, p2):
   dx = p2[0] - p1[0]
   dy = p2[1] - p1[1]
   return math.sqrt(dx * dx + dy * dy)
def Centroid(pts):
   x = 0
   y = 0
   for a in pts:
      x += a[0]
      y += a[1]
   x /= len(pts)
   y /= len(pts)
   return [x,y]
def releaseDraw(event):
    global draw
    draw.currentpoints.append([event.x,event.y])
    draw.canvas.create_line(draw.currentpoints[len(draw.currentpoints)-1][0],draw.currentpoints[len(draw.currentpoints)-1][1],event.x,event.y,fill = "blue",width=7)
    draw.strokes.append(draw.currentpoints)
    if(len(draw.currentpoints)<10):
        clicked3Draw(0)
    draw.currentpoints=[]
def clicked3Draw( event ):
    global draw
    if len(draw.strokes)>0:
        popped=draw.strokes.pop()
        draw.canvas.delete("all")
        draw.drawAllNormal(draw.strokes,"blue")
##        draw.drawPoints(popped,"gray94")
def Resample(pts,n):
   points=pts[:]
   I=PathLength(points)/(n-1)
   D=0
   newpoints=[points[0]]
   i=1
   while i<len(points):
      d=Distance(points[i-1],points[i])
      if (D+d)>=I:
         qx=points[i-1][0]+((I-D)/d)*(points[i][0]-points[i-1][0])
         qy=points[i-1][1]+((I-D)/d)*(points[i][1]-points[i-1][1])
         q=[qx,qy]
         points.insert(i,q) 
         newpoints.append(q)
         D=0
      else:
         D+=d
      i+=1
   if(len(newpoints)<n):
      newpoints.append(pts[len(pts)-1])
   return newpoints
def getRoundest(pts):
    minv=99999
    result=-1
    for i in range(len(pts)):
        error=RecognizeCircle(pts[i])
        if(error<minv):
            minv=error
            result=i
    return result
def getRadius(pts):
    data=[]
    center=Centroid(pts)
    mean=0
    for p in pts:
        mean+=Distance(p,center)
    mean=mean/len(pts)
    return mean
def BoundingBox(pts):
   minX=99999999.0
   maxX=-minX
   minY=99999999.0
   maxY=-minY
   for a in pts:
      minX=min(minX,float(a[0]))
      minY=min(minY,float(a[1]))
      maxX=max(maxX,float(a[0]))
      maxY=max(maxY,float(a[1]))
   return [minX, minY, maxX - minX, maxY - minY]
def ScaleTo(pts, size):
    B=BoundingBox(pts)
    newpoints=[]
    return pts*[size/B[2],size/B[3]]
def IndicativeAngle(pts):
   c = Centroid(pts)
   return math.atan2(c[1] - pts[0][1], c[0] - pts[0][0]);
def RotateBy(pts, radians):
   c = Centroid(pts);
   cos = math.cos(radians);
   sin = math.sin(radians);
   newpoints =[]
   for a in pts:
      qx=(a[0]-c[0])*cos-(a[1]-c[1])*sin+c[0]
      qy=(a[0]-c[0])*sin+(a[1]-c[1])*cos+c[1]
      newpoints.append([qx,qy])
   return newpoints
def compareStrokes(ptsa,ptsb):
    error=0
    for i in range(len(ptsa)):
        error+=Distance(ptsa[i],ptsb[i])
    return error/(len(ptsa))
def RecognizeCircle(pts):
    num=250
    size=100
    r=size/2
    c=Centroid(pts)
    a=IndicativeAngle(pts)
    newpts=RotateBy(pts,math.pi-a)
    newpts=Resample(newpts,num)
    newpts=TranslateTo(newpts,[0,0])
    newpts=ScaleTo(newpts, 100)
    Rcircle=getCircle(r,num)
    Lcircle=Rcircle[:]
    Lcircle.reverse()
    errorR=compareStrokes(Rcircle,newpts)
    errorL=compareStrokes(Lcircle,newpts)
    error=min(errorR,errorL)
    return error
def getCircle(r,n):
    newpoints=[]
    for i in range(0,n):
        newpoints.append([r*math.cos(2*math.pi*i/n),r*math.sin(2*math.pi*i/n)])
    return newpoints
def linealizarNew(datos,iteraciones):
    arrays=[datos]
    while(iteraciones>0):
        newarrays=[]
        subscore=getSublineScore(arrays)
        toremove=arrays[subscore[0]]

        for i in range(len(arrays)):
            if i==subscore[0]:
                newarrays.append(toremove[:subscore[1]])
                newarrays.append(toremove[subscore[1]:])
            else:
                newarrays.append(arrays[i])
        arrays=newarrays
        iteraciones-=1
    
    res=[]
    res.append(arrays[0][0])
    for a in arrays:
        res.append(a[len(a)-1])
    return res
    
def getLineScore(datos):
    Pi=datos[0]
    Pf=datos[len(datos)-1]
    Pd=[Pf[0]-Pi[0],Pf[1]-Pi[1]]
    maxD=0
    curri=-1
    Pideal=[0,0]
    for i in range(len(datos)):
        Pideal[0]=Pi[0]+((float(i)/len(datos))*Pd[0])
        Pideal[1]=Pi[1]+((float(i)/len(datos))*Pd[1])
        d=((Pideal[0]-datos[i][0])**2)+((Pideal[1]-datos[i][1])**2)
        if(d>maxD):
            maxD=d
            curri=i
    return [maxD,curri]
def getSublineScore(array):
    maxScore=[0,0]
    linei=-1
    for i in range(len(array)):
        score=getLineScore(array[i])
        if(score[0]>maxScore[0]):
            maxScore=[score[0],score[1]]
            linei=i
    return [linei,maxScore[1]]
class VisionFrame(Frame):
    canvas=0
    anim=0
    currenti=-1
    buttonraw=0
    buttonsmooth=0
    rawgif=0
    smoothgif=0
    buttonframe=0
    topframe=0
    def __init__(self,master):
        Frame.__init__(self,master,bd=10,relief=RAISED)
        self.grid(column=1,row=1,sticky=W+E+N+S)
        self.canvas=Canvas(self)
        self.anim=0
        self.canvas.pack(expand=1,fill=BOTH)
        self.rawgif=PhotoImage(file="raw.gif")
        self.smoothgif=PhotoImage(file="smooth.gif")
        
        self.buttonframe=Frame(self.canvas)
        self.buttonframe.pack(side=RIGHT)
        self.buttonraw=Button(self.buttonframe,image=self.rawgif,command=self.rawAction,relief=SUNKEN)
        self.buttonraw.pack(side=TOP)
        self.buttonsmooth=Button(self.buttonframe,image=self.smoothgif,command=self.smoothAction)
        self.buttonsmooth.pack(side=TOP)
    def rawAction(self):
        if(self.buttonraw["relief"]==RAISED):
            self.buttonraw.config(relief=SUNKEN)
            self.buttonsmooth.config(relief=RAISED)
            self.dibujar(self.currenti)
            
    def smoothAction(self):
        if(self.buttonsmooth["relief"]==RAISED):
            self.buttonsmooth.config(relief=SUNKEN)
            self.buttonraw.config(relief=RAISED)
            self.dibujar(self.currenti)
    def setAnimation(self,anim):
        self.anim=anim
    def dibujar(self,i):
        if(self.anim==0 or i==-1):
            return
        self.currenti=i
        self.canvas.delete("all")
        if(self.buttonraw["relief"]==SUNKEN):
            self.anim.dibujarFrame(i)
        else:
            self.anim.dibujarCurva(i)
        self.anim.dibujarProgreso(i)
global fetcher
global draw
global vision
global primera
primera=0
fetcher=0
draw=0
w=0
def drawLines(pt,color):
    global primera
    if primera==0:
        primera=pt
    else:
        vision.canvas.create_line(primera[0],primera[1],pt[0],pt[1],fill =color ,width=3)
        primera=pt
def drawLinesSlide(pt,color):
    global primera
    if primera==0:
        primera=pt
    else:
        vision.canvas.create_line(primera[0],primera[1],pt[0],pt[1],fill =color ,width=3)
        primera=pt
def drawEmptyOval(pt,rad,color):
    vision.canvas.create_oval(pt[0]-rad,pt[1]-rad,pt[0]+rad,pt[1]+rad,outline=color,width=3)
def drawOvals(pt,color):
    vision.canvas.create_oval(pt[0]-5,pt[1]-5,pt[0]+5,pt[1]+5,fill=color)
def init():
    global fetcher
    global draw
    global vision
    global master
    global onmarchvalue
    onmarchvalue=BooleanVar()
    global toolbar
    toolbar = Frame(master)
    global menubar
    menubar = Menu(toolbar,tearoff=False)
    fileMenu = Menu(toolbar,tearoff=False)
    global recentMenu
    recentMenu = Menu(toolbar,tearoff=False)
     
    menubar.add_cascade(label="Archivo", menu=fileMenu)
    fileMenu.add_command(label="Abrir", command=openCallBack)
    fileMenu.add_cascade(label="Abrir reciente", menu=recentMenu)
    
    fileMenu.add_command(label="Salir")
    
    fetcher=FetcherFrame(master)
    draw=DrawFrame(master)
    vision=VisionFrame(master)
    
    infotoolbar=Frame(master,height=60)
    global labelY
    labelY=Label(infotoolbar,width=20)
    labelY.pack(side='right')
    global labelX
    labelX=Label(infotoolbar,width=10)
    labelX.pack(side='right')
    global labelIndex
    labelIndex=Label(infotoolbar,width=10)
    labelIndex.pack(side='right')
    global labelInfo
    labelInfo=Label(infotoolbar,width=20)
    labelInfo.pack(side='right')
    
    vistasSubMenu=Menu(toolbar,tearoff=False)
    master.configure(menu=menubar)
    wid=1000.0
    h=450.0
    ws = master.winfo_screenwidth()
    hs = master.winfo_screenheight()
    x = (ws/2) - (wid/2) 
    y = (hs/2) - (h/2)
    master.geometry('%dx%d+%d+%d' % (wid, h, x, y))
    master.deiconify()

global tasks
tasks=[]
isdone=False
global animation
animation=0

def avanzarWait(tk,num,txt):
    tk.msg.config(text=txt)
    tk.progress["value"]+=num
class WaitScreen(Tk):
    msg=0
    progress=0
    frame=0
    hilo=0
    def __init__(self,title):
        width=300
        height=60
        Tk.__init__(self)
        self.title(title)
        self.msg=Message(self, text="cargando...",width=600)
        self.msg.pack(expand=1,fill=X,side=TOP)
        self.progress = ttk.Progressbar(self, maximum=100)
        self.progress.pack(expand=1,fill=X,side=TOP)
        self.maxsize(width,height)
        self.minsize(width,height)
        ws = master.winfo_screenwidth()
        hs = master.winfo_screenheight()
        x = (ws/2) - (width/2) 
        y = (hs/2) - (height/2)
        self.geometry('%dx%d+%d+%d' % (width,height, x, y))
    def start(self,funcion):
        self.hilo=threading.Thread(target=funcion)
        self.hilo.setDaemon(True)
        self.hilo.start()
    def avanzar(self,n,title):
        global tasks
        tasks.append(lambda txt=title,tk=self,num=n:avanzarWait(tk,num,txt))
    def terminar(self):
        global tasks
        tasks.append(self.destroy)
##try_mainloop()
##initcall()
init()
new_mainloop()
